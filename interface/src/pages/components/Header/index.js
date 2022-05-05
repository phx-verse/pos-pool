import {createPortal} from 'react-dom'
import {Link} from 'react-router-dom'
import {Layout, Button, Select} from 'antd'
import {useTranslation} from 'react-i18next'
import {useTryActivate, useAccount} from '../../../hooks/useWallet';
import {isTestNetEnv} from '../../../utils'
import NotAllow from '../../../images/not-allow.png'
import i18n from '../../../../public/locales'
import useCurrentSpace from '../../../hooks/useCurrentSpace'
import useCurrentNetwork from '../../../hooks/useCurrentNetwork'
import useIsNetworkMatch from '../../../hooks/useIsNetworkMatch'

const {Option} = Select
const {Header} = Layout
const isTest = isTestNetEnv()

function HeaderComp() {
  const {t} = useTranslation()
  const address = useAccount()
  const tryActivate = useTryActivate()
  const isNetworkMatch = useIsNetworkMatch()
  const networkError = !isNetworkMatch
  const currentSpace = useCurrentSpace()
  const currentNetwork = useCurrentNetwork()
  
  return (
    <Header style={{width: '100%', height: 'fit-content', padding: 0}}>
      {isTest && (
        <div className="w-full h-[64px] leading-[64px] text-[#f3504f] bg-[#f3504f] bg-opacity-20 z-[49] text-[16px] text-center border-b border-[#f3504f]">
          {t('Header.test_note')}
        </div>
      )}
      <div className="flex justify-between text-white bg-main-back bg-opacity-0 px-[50px]">
        <div>
          <Link
            to="/pool-manage"
          >
            {t('Header.pos_pool')}
          </Link>
        </div>
        <div className="flex items-center">
          <Select
            style={{marginRight: '20px'}}
            defaultValue={i18n.language}
            onChange={lng => i18n.changeLanguage(lng)}
          >
            <Option value="en">English</Option>
            <Option value="vn">Vietnamese</Option>
            <Option value="id">Indonesian</Option>
            <Option value="ko">Korean</Option>
            {/* <Option value="zh">中文</Option> */}
          </Select>
          {currentSpace && address && <div>{address}</div>}
          {currentSpace && !address && (
            <Button type="primary" onClick={tryActivate}>
              {t(currentSpace === 'core' ? 'Header.connect_fluent' : 'Header.connect_metamask')}
            </Button>
          )}
        </div>
      </div>

      {networkError &&
        createPortal(
          <div className="fixed top-0 left-0 w-[100vw] h-[100vh] bg-black bg-opacity-25 z-50">
            <div className="absolute top-[40%] left-[50%] translate-x-[-50%] translate-y-[-50%] flex flex-col justify-center items-center w-[480px] h-[390px] px-[28px] py-[12px] bg-white shadow rounded-md">
              <img
                className="w-[340px] h-[240px]"
                src={NotAllow}
                alt="not allow imgs"
              />
              <p className="text-[32px] leading-[32px] text-[#333] my-[16px] font-bold">
                {t('Header.error')}
              </p>
              <p className="text-[16px] leading-[24px] text-[#999] my-0 font-medium">
                {t('Header.unspport_network_switch', { network: currentNetwork?.name || ''})}
              </p>
            </div>
          </div>,
          document.body,
        )}
    </Header>
  )
}

export default HeaderComp
